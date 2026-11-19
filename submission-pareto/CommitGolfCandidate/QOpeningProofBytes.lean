import CommitGolfCandidate.QOpeningABI

namespace TwoPermutationPrototype.QOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling
  RiscvZkvm.Rv64 OracleComp

def trapdoorHeap {s : Submission} (trapdoor : BitVec (8 * s.sizes.trapdoor)) (node : Nat) : BitVec 256 :=
  trapdoor.extractLsb' (256*node) 256

def trapdoorSalt {s : Submission} (trapdoor : BitVec (8 * s.sizes.trapdoor)) (index : Index) : BitVec 128 :=
  trapdoor.extractLsb' (8 * (1811943424 + 16 * index.val)) 128

def proofFromTrapdoor {s : Submission} (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) : Proof :=
  (positions.sort (· ≤ ·)).flatMap (fun i => lowerRecord false (trapdoorHeap (s := s) trapdoor)
    i (trapdoorSalt (s := s) trapdoor i)) ++
    (openingNodes positions).flatMap (fun node => digestBytes (trapdoorHeap (s := s) trapdoor node))

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

private theorem lower_record_bytes (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (index : Index) (ordinal : Nat)
    (contents : LowerContents s trapdoor positions state index ordinal 16) :
    bytesAt state (recordBase ordinal) 528 =
      lowerRecord false (trapdoorHeap (s := s) trapdoor) index (trapdoorSalt (s := s) trapdoor index) := by
  change bytesAt state (recordBase ordinal) (16+32*16) = _
  rw [bytes_at_append]
  have nonce := bytes_at_serialized state (recordBase ordinal) 16 (trapdoorSalt (s := s) trapdoor index)
    contents.nonce
  unfold lowerRecord
  rw [nonce]
  have chunks : bytesAt state (recordBase ordinal+16) (32*(List.range 16).length) =
      (List.range 16).flatMap (fun level => digestBytes
        (trapdoorHeap (s := s) trapdoor (lowerNode index level ^^^ 1))) := by
    apply bytes_at_chunks
    intro j inside
    have bounded : j < 16 := by simpa using inside
    have exactBytes := bytes_at_serialized state (siblingDest ordinal j) 32 _ (contents.sibling j bounded)
    rw [List.getElem_range]
    exact exactBytes
  change saltBytes (trapdoorSalt (s := s) trapdoor index) ++
      bytesAt state (recordBase ordinal+16) (32*16) =
    saltBytes (trapdoorSalt (s := s) trapdoor index) ++
      (List.range 16).flatMap (fun level => digestBytes
        (trapdoorHeap (s := s) trapdoor (lowerNode index level ^^^ 1)))
  rw [← chunks, List.length_range]

end TwoPermutationPrototype.QOpening
