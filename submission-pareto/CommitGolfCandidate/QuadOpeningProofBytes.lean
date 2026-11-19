import CommitGolfCandidate.QuadOpeningABI
import CommitGolfCandidate.QuadOpeningModel

/-! The decoded opening output is `proofFromTrapdoor`. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp Sampling
open QOpening (OpeningLayout trapdoorSalt proofBase nonceBase trapdoorBase)

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

theorem record_bytes (s : Submission) (layout : OpeningLayout s) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (o : Nat) (present : o < positions.card)
    (out : Inv (s.initialState .opening (trapdoor, positions)) state (wordSource positions) (178*positions.card)) :
    bytesAt state (proofBase+1424*o) 1424 =
      trapdoorRecord (s := s) trapdoor ((positions.sort (· ≤ ·))[o]'(by simpa using present)) := by
  let init := s.initialState .opening (trapdoor, positions)
  let index := (positions.sort (· ≤ ·))[o]'(by simpa using present)
  have named : ordinalIndex positions o = index.val := ordinal_index positions o present
  have inside := index.isLt
  have hL : LENGTH = 16777216 := rfl
  have proofAligned : proofBase % 8 = 0 := by decide
  have word (d : Nat) (live : d < 178) : state.getMem (BitVec.ofNat 64 (proofBase+1424*o+8*d)) =
      init.getMem (BitVec.ofNat 64 (wordSource positions (178*o+d))) := by
    rw [show proofBase+1424*o+8*d = proofBase+8*(178*o+d) by omega]
    exact out.output _ (by omega)
  -- salt
  have saltRead : readBuffer state (proofBase+1424*o) 16 = trapdoorSalt (s := s) trapdoor index := by
    have copied := QOpening.copied_buffer init state (nonceBase+16*index.val) (proofBase+1424*o) 2
      (by have : nonceBase % 8 = 0 := by decide
          omega) (by omega) (by decide) (fun w hw => by
        rw [word w (by omega), word_source_salt positions o w hw, named])
    exact copied.trans (QOpening.input_nonce s layout trapdoor positions index)
  have part₁ : bytesAt state (proofBase+1424*o) 16 = saltBytes (trapdoorSalt (s := s) trapdoor index) :=
    bytes_at_serialized state _ 16 _ saltRead
  -- children
  have child (k j : Nat) (hk : k < 11) (hj : j < 4) :
      bytesAt state (proofBase+1424*o+16+128*k+32*j) 32 =
        digestBytes (pentaTrapdoorNode trapdoor k (pentaNeighbour index k j)) := by
    have source := neighbour_source index.val k j inside hk hj
    have copied := QOpening.copied_buffer init state
      (trapdoorBase+pentaSlotOffset k (neighbourNat index.val k j)) (proofBase+1424*o+16+128*k+32*j) 4
      source.2.1 (by omega) (by decide) (fun w hw => by
        rw [show proofBase+1424*o+16+128*k+32*j+8*w = proofBase+1424*o+8*(2+16*k+4*j+w) by omega,
          word _ (by omega), show 178*o+(2+16*k+4*j+w) = 178*o+2+16*k+4*j+w by omega,
          word_source_level positions o k j w hk hj hw, named])
    have slice := QOpening.input_trapdoor_slice s layout trapdoor positions
      (pentaSlotOffset k (neighbourNat index.val k j)) 32 (by
        have := source.2.2.2
        unfold QOpening.trapdoorBytes
        omega)
    have value : readBuffer state (proofBase+1424*o+16+128*k+32*j) 32 =
        pentaTrapdoorNode trapdoor k (pentaNeighbour index k j) := copied.trans slice
    exact bytes_at_serialized state _ 32 _ value
  have part₂ : bytesAt state (proofBase+1424*o+16) (128*(List.range PENTA_LEVELS).length) =
      (List.range PENTA_LEVELS).flatMap fun k =>
        (List.range 4).flatMap fun j => digestBytes (pentaTrapdoorNode trapdoor k (pentaNeighbour index k j)) := by
    apply bytes_at_chunks
    intro k hk
    have bound : k < 11 := by simpa [PENTA_LEVELS] using hk
    rw [List.getElem_range]
    have inner := bytes_at_chunks state (proofBase+1424*o+16+128*k) 32 (List.range 4)
      (fun j => digestBytes (pentaTrapdoorNode trapdoor k (pentaNeighbour index k j)))
      (fun j hj => by
        rw [List.getElem_range]
        exact child k j bound (by simpa using hj))
    simpa using inner
  have split : bytesAt state (proofBase+1424*o) 1424 =
      bytesAt state (proofBase+1424*o) 16 ++
        bytesAt state (proofBase+1424*o+16) (128*(List.range PENTA_LEVELS).length) := by
    rw [show (1424 : Nat) = 16+128*(List.range PENTA_LEVELS).length by simp [PENTA_LEVELS], bytes_at_append]
  rw [split, part₁, part₂]
  rfl

theorem read_opening_proof (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (result : Execution)
    (physical : OpenPhysical s trapdoor positions result) :
    s.readProof result = proofFromTrapdoor (s := s) trapdoor positions := by
  have success := opening_success s abi trapdoor positions result physical
  simp only [Submission.readProof, success, ite_true, physical.length, abi.toOpeningLayout.proof]
  change bytesAt result.state proofBase (proofLength positions) = _
  have length : (positions.sort (· ≤ ·)).length = positions.card := Finset.length_sort _
  rw [proofLength, ← length, proofFromTrapdoor]
  apply bytes_at_chunks
  intro o inside
  exact record_bytes s abi.toOpeningLayout trapdoor positions result.state o (by simpa using inside)
    physical.output

/-- The full executable opener refines this serialization function for every trapdoor. -/
theorem scheme_open_bytes (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) :
    s.scheme.opening trapdoor positions = pure (proofFromTrapdoor (s := s) trapdoor positions) := by
  obtain ⟨result, ran, physical⟩ := opening_physical s abi trapdoor positions
  change (s.readProof <$> s.run .opening (trapdoor, positions)) = _
  rw [ran]
  simp [read_opening_proof s abi trapdoor positions result physical]

theorem opening_proof_size (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (result : Execution) (physical : OpenPhysical s trapdoor positions result) :
    (s.readProof result).length = (result.state.getReg .x11).toNat := by
  simp only [Submission.readProof, opening_success s abi trapdoor positions result physical,
    ite_true, List.length_map, List.length_range]

end TwoPermutationPrototype.QuadOpening
