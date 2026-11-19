import CommitGolfCandidate.TwoPermutationPackedOpeningABI
import CommitGolfCandidate.TwoPermutationPackedOpeningModel

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp Sampling
open Opening (OpeningLayout trapdoorHeap trapdoorSalt sortedIndex lowerNode proofBase openingNodes groupsBefore)

private def bytesAt (state : MachineState) (address count : Nat) : List Byte :=
  (List.range count).map fun j => state.getByte (BitVec.ofNat 64 (address+j))

private theorem bytes_at_append (state : MachineState) (address left right : Nat) :
    bytesAt state address (left+right) =
      bytesAt state address left ++ bytesAt state (address+left) right := by
  simp [bytesAt, List.range_add, List.map_append, List.map_map, Function.comp_def, Nat.add_assoc]

private theorem bytes_at_serialized (state : MachineState) (address count : Nat)
    (value : BitVec (8*count)) (serialization : readBuffer state address count = value) :
    bytesAt state address count = List.ofFn (fun i : Fin count => value.extractLsb' (8*i.val) 8) := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i left right
    have inside : i < count := by simpa [bytesAt] using left
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [← serialization, read_buffer_byte state address count i inside]

private theorem bytes_at_chunks {α : Type} (state : MachineState) (address width : Nat) (items : List α)
    (itemBytes : α → List Byte)
    (reads : ∀ j (inside : j < items.length),
      bytesAt state (address+width*j) width = itemBytes items[j]) :
    bytesAt state address (width*items.length) = items.flatMap itemBytes := by
  induction items generalizing address with
  | nil => simp [bytesAt]
  | cons first rest ih =>
    have head := reads 0 (by simp)
    have tail : ∀ j (inside : j < rest.length),
        bytesAt state (address + width + width*j) width = itemBytes rest[j] := by
      intro j inside
      have same := reads (j+1) (by simpa)
      simpa only [List.getElem_cons_succ, Nat.mul_succ, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using same
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm (width*rest.length) width, bytes_at_append,
      List.flatMap_cons, ih (address+width) tail]
    simpa using head

private theorem proof_digest_byte (packed : Bool) (digest : BitVec 256) (i : Nat)
    (bound : i < (proofDigestBytes packed digest).length) :
    (proofDigestBytes packed digest)[i] = digest.extractLsb' (8*i) 8 := by
  cases packed <;> simp only [proofDigestBytes, Bool.false_eq_true, ite_false, ite_true,
    digestBytes, List.getElem_ofFn, List.getElem_take]

private theorem lower_record_bytes (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (state : MachineState)
    (ordinal : Nat) (present : ordinal < positions.card)
    (contents : CompletedRecords s trapdoor positions state (ordinal+1)) :
    bytesAt state (recordBase ordinal) 498 =
      lowerRecord true (trapdoorHeap (s := s) trapdoor) (sortedIndex positions ordinal present)
        (trapdoorSalt (s := s) trapdoor (sortedIndex positions ordinal present)) := by
  let initial := s.initialState .opening (trapdoor, positions)
  let index := sortedIndex positions ordinal present
  let hash := trapdoorHeap (s := s) trapdoor
  let salt := trapdoorSalt (s := s) trapdoor index
  obtain ⟨nonce, path⟩ := contents ordinal present (by omega)
  have serialized : readBuffer state (recordBase ordinal) 16 = salt := by
    have copied : readBuffer state (recordBase ordinal) 16 = readBuffer initial (nonceAddress index) 16 := by
      unfold readBuffer
      apply congrArg (BitVec.ofNat 128)
      apply Finset.sum_congr rfl
      intro i hi
      rw [nonce i (Finset.mem_range.mp hi)]
    rw [copied]
    exact Opening.input_nonce s layout trapdoor positions index
  have nonceBytes : bytesAt state (recordBase ordinal) 16 = saltBytes salt :=
    bytes_at_serialized state (recordBase ordinal) 16 salt serialized
  have digest (level : Nat) (live : level < 16) :
      bytesAt state (siblingDestination ordinal level) (siblingWidth level) =
      proofDigestBytes (level != 0) (hash (lowerNode index level ^^^ 1)) := by
    have source : readBuffer initial (siblingAddress index level) 32 =
        hash (lowerNode index level ^^^ 1) :=
      Opening.input_digest s layout trapdoor positions _ (Opening.lower_swap_bound index level)
    have width : (proofDigestBytes (level != 0) (hash (lowerNode index level ^^^ 1))).length =
        siblingWidth level := by
      rw [proof_digest_length]
      by_cases first : level = 0 <;> simp [siblingWidth, first]
    apply List.ext_getElem
    · simp [bytesAt, width]
    · intro i inside outBound
      have bound : i < siblingWidth level := by simpa [bytesAt] using inside
      have under : i < 32 := by unfold siblingWidth at bound; split at bound <;> omega
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      rw [path level live i bound, ← read_buffer_byte initial (siblingAddress index level) 32 i under, source]
      exact (proof_digest_byte (level != 0) _ i outBound).symm
  have later : bytesAt state (recordBase ordinal+48) (30*(List.range 15).length) =
      (List.range 15).flatMap (fun j => proofDigestBytes true (hash (lowerNode index (j+1) ^^^ 1))) := by
    apply bytes_at_chunks
    intro j inside
    have bound : j < 15 := by simpa using inside
    rw [List.getElem_range]
    have here := digest (j+1) (by omega)
    simpa [siblingDestination, siblingOffset, siblingWidth, show j+1 ≠ 0 by omega, Nat.add_assoc] using here
  change bytesAt state (recordBase ordinal) (16+(32+30*15)) = lowerRecord true hash index salt
  rw [bytes_at_append, nonceBytes]
  change saltBytes salt ++ bytesAt state (recordBase ordinal+16) (32+30*15) = _
  rw [bytes_at_append, show recordBase ordinal+16 = siblingDestination ordinal 0 from rfl]
  rw [show 32 = siblingWidth 0 from rfl, digest 0 (by decide)]
  rw [show siblingDestination ordinal 0+siblingWidth 0 = recordBase ordinal+48 by
    simp [siblingDestination, siblingOffset, siblingWidth, Nat.add_assoc]]
  rw [show (15:Nat) = (List.range 15).length by decide, later]
  unfold lowerRecord
  rw [show List.range 16 = 0 :: (List.range 15).map (fun j => j+1) from by decide,
    List.flatMap_cons, List.flatMap_map]
  simp only [Bool.true_and, Nat.reduceBEq, Bool.not_true, lowerNode]
  congr 2

/-- The decoded ABI output is the exact lower records and canonical cap footer. -/
theorem read_opening_proof (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) (result : Execution)
    (physical : OpenPhysical s trapdoor positions result) :
    s.readProof result = proofFromTrapdoor (s := s) trapdoor positions := by
  have fit : (result.state.getReg .x11).toNat ≤ s.sizes.proof := by
    rw [physical.length]
    exact (proof_fits_every_cardinality positions).trans abi.capacity
  have success : s.openingSucceeded result = true := by
    simp [Submission.openingSucceeded, physical.success, fit]
  simp only [Submission.readProof, success, ite_true, physical.length, abi.toOpeningLayout.proof]
  change bytesAt result.state proofBase (proofLength positions) = _
  rw [proofLength, bytes_at_append, proofFromTrapdoor]
  congr 1
  · have length : (positions.sort (· ≤ ·)).length = positions.card := Finset.length_sort _
    rw [← length]
    apply bytes_at_chunks
    intro j inside
    have present : j < positions.card := by simpa using inside
    have lower : CompletedRecords s trapdoor positions result.state (j+1) := by
      intro prior live earlier
      exact physical.lower prior live (by omega)
    exact lower_record_bytes s abi.toOpeningLayout trapdoor positions result.state j present lower
  · apply bytes_at_chunks
    intro j inside
    have footer := physical.footer j inside
    apply List.ext_getElem
    · simp [bytesAt, proof_digest_length]
    · intro i left right
      have byte : i < 30 := by simpa [bytesAt] using left
      let node := (openingNodes positions)[j]
      let initial := s.initialState .opening (trapdoor, positions)
      let source := Opening.capDigestAddress node
      have nodeBound : node < 512 := by
        have nonempty : positions.card ≠ 0 := by intro empty; simp [openingNodes, empty] at inside
        apply Opening.cap_frontier_nodes_small (groupsBefore positions positions.card) 1 8 Opening.cap_span_root
        have member : node ∈ openingNodes positions := List.getElem_mem inside
        simpa [openingNodes, nonempty] using member
      have whole : readBuffer initial source 32 = trapdoorHeap (s := s) trapdoor node := by
        exact Opening.input_digest s abi.toOpeningLayout trapdoor positions node
          (nodeBound.trans_le (by decide : 512 ≤ 2*LENGTH))
      have slice : readBuffer initial source 30 =
          (trapdoorHeap (s := s) trapdoor node).extractLsb' 0 240 := by
        have low := read_buffer_slice initial source 32 0 30 (by decide)
        simpa only [whole, Nat.add_zero, Nat.mul_zero] using low.symm
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      change result.state.getByte (BitVec.ofNat 64 (recordBase positions.card+30*j+i)) = _
      have footerValue : readBuffer result.state (recordBase positions.card+30*j) 30 =
          (trapdoorHeap (s := s) trapdoor node).extractLsb' 0 240 := footer
      rw [← read_buffer_byte result.state _ 30 i byte, footerValue, ← slice, read_buffer_byte initial source 30 i byte]
      rw [← read_buffer_byte initial source 32 i (by omega), whole]
      simp only [proofDigestBytes, ite_true, List.getElem_take, digestBytes, List.getElem_ofFn]
      rfl

/-- The full executable opener refines this serialization function for every trapdoor. -/
theorem scheme_open_bytes_with (recordsExecute : RecordsExecute) (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) :
    s.scheme.opening trapdoor positions = pure (proofFromTrapdoor (s := s) trapdoor positions) := by
  obtain ⟨result, ran, physical⟩ := opening_physical_with recordsExecute s abi trapdoor positions
  change (s.readProof <$> s.run .opening (trapdoor, positions)) = _
  rw [ran]
  simp [read_opening_proof s abi trapdoor positions result physical]

end TwoPermutationPrototype.PackedOpening
