import CommitGolfCandidate.TwoPermutationCheckLoader
import CommitGolfCandidate.TwoPermutationOpeningABI
import CommitGolfCandidate.TwoPermutationHonestLower

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

/-- An honest checker input, serialized by the trusted loader like any other input. -/
def honestCheckInput (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    CheckInput :=
  let view := honestView (transcriptBuilder false) oracle.compression
    (BiPermutation.equiv Block oracle.permutation) message positions salts
  ⟨view.1, positions, message.restrict positions, view.2⟩

def honestHeap (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → Digest :=
  transcriptHeap false oracle.compression
    (fullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)

def honestOrder (positions : Positions) : List {index // index ∈ positions} :=
  positions.attach.sort (fun i j => i.val ≤ j.val)

theorem honest_order_length (positions : Positions) : (honestOrder positions).length = positions.card := by
  simp [honestOrder]

def honestIndex (positions : Positions) (ordinal : Nat) (present : ordinal < positions.card) :
    {index // index ∈ positions} :=
  (honestOrder positions)[ordinal]'(by simpa only [honest_order_length] using present)

private theorem honest_groups (positions : Positions) :
    (honestOrder positions).map (capGroup ∘ Subtype.val) = Opening.groupsBefore positions positions.card := by
  unfold Opening.groupsBefore
  have size : (positions.sort (· ≤ ·)).length = positions.card := by simp
  rw [← size, List.take_length, ← CommitGolfCandidate.sorted_value_indices positions, List.map_map]
  rfl

theorem honest_proof_parts (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).proof =
      (honestOrder positions).flatMap (fun i : {i // i ∈ positions} =>
        lowerRecord false (honestHeap oracle message salts) i.val (salts i.val)) ++
      (Opening.openingNodes positions).flatMap (fun node => digestBytes (honestHeap oracle message salts node)) := by
  change _ ++ frontierProof false _ ((honestOrder positions).map (capGroup ∘ Subtype.val)) = _
  rw [honest_groups]
  have size : (Opening.groupsBefore positions positions.card).length = positions.card := by
    simp [Opening.groupsBefore]
  have empty : (Opening.groupsBefore positions positions.card).isEmpty = true ↔ positions.card = 0 := by
    rw [List.isEmpty_iff]
    simpa only [size] using (List.length_eq_zero_iff (l := Opening.groupsBefore positions positions.card)).symm
  unfold frontierProof Opening.openingNodes
  by_cases noPositions : positions.card = 0
  · rw [ite_eq_left (empty.mpr noPositions), ite_eq_left noPositions, List.flatMap_nil]
    rfl
  · have someGroup : (Opening.groupsBefore positions positions.card).isEmpty = false :=
      Bool.eq_false_of_not_eq_true (mt empty.mp noPositions)
    rw [ite_eq_right (by rw [someGroup]; decide), ite_eq_right noPositions]
    rfl

private theorem fixed_flatmap_length {α β : Type} (f : α → List β) (width : Nat)
    (fixed : ∀ a, (f a).length = width) (xs : List α) :
    (xs.flatMap f).length = width * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [fixed, ih, Nat.mul_succ, Nat.add_comm]

private theorem fixed_flatmap_byte {α β : Type} (f : α → List β) (width : Nat)
    (fixed : ∀ a, (f a).length = width) (xs : List α) (ordinal offset : Nat)
    (present : ordinal < xs.length) (inside : offset < width) :
    (xs.flatMap f)[width*ordinal+offset]? = (f xs[ordinal])[offset]? := by
  induction xs generalizing ordinal with
  | nil => simp at present
  | cons x xs inductionHypothesis =>
    cases ordinal with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      exact List.getElem?_append_left (by simpa only [fixed] using inside)
    | succ ordinal =>
      simp only [List.flatMap_cons, Nat.mul_succ, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [fixed]; omega), fixed,
        show width*ordinal+width+offset-width = width*ordinal+offset by omega]
      exact inductionHypothesis ordinal (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using present)

theorem honest_proof_length (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).proof.length = Opening.openingLength positions := by
  rw [honest_proof_parts, List.length_append,
    fixed_flatmap_length _ 528 (fun _ => lower_record_length false _ _ _) _,
    fixed_flatmap_length _ 32 (fun _ => digestBytes_length _) _, honest_order_length]
  rfl

theorem honest_input_records_fit (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    528*positions.card ≤ (honestCheckInput oracle message positions salts).proof.length := by
  rw [honest_proof_length]
  exact Nat.le_add_right _ _

theorem honest_input_empty (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (empty : positions.card = 0) :
    (honestCheckInput oracle message positions salts).proof.length = 0 := by
  rw [honest_proof_length]
  simp [Opening.openingLength, Opening.openingNodes, empty]

theorem honest_input_admitted (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).proof.length ≤ Assembly.submission.sizes.proof := by
  rw [honest_proof_length]
  exact (Opening.opening_length_bound positions).trans Assembly.opening_abi.capacity

theorem honest_input_root (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    readBuffer (Assembly.submission.initialState .check (honestCheckInput oracle message positions salts))
      Assembly.submission.layout.commitment 32 = honestHeap oracle message salts 1 :=
  check_input_commitment (honestCheckInput oracle message positions salts)

theorem honest_input_index (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (ordinal : Nat) (present : ordinal < positions.card) :
    (Assembly.submission.initialState .check (honestCheckInput oracle message positions salts)).getMem
      (BitVec.ofNat 64 (Assembly.submission.layout.indices+8*ordinal)) =
      BitVec.ofNat 64 (honestIndex positions ordinal present).val.val := by
  let input := honestCheckInput oracle message positions salts
  have ordered := check_input_value_index input ordinal present
  have initial := check_input_position input ordinal present
  exact initial.trans (congrArg (fun index : Index => BitVec.ofNat 64 index.val) ordered.symm)

theorem honest_input_value (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (ordinal : Nat) (present : ordinal < positions.card) :
    readBuffer (Assembly.submission.initialState .check (honestCheckInput oracle message positions salts))
      (Assembly.submission.layout.values+256*ordinal) 256 = message (honestIndex positions ordinal present) :=
  check_input_value (honestCheckInput oracle message positions salts) ordinal present

private theorem honest_record_byte (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal offset : Nat)
    (present : ordinal < positions.card) (inside : offset < 528) :
    (honestCheckInput oracle message positions salts).proof[528*ordinal+offset]? =
      (lowerRecord false (honestHeap oracle message salts) (honestIndex positions ordinal present)
        (salts (honestIndex positions ordinal present)))[offset]? := by
  let record := fun i : {i // i ∈ positions} => lowerRecord false (honestHeap oracle message salts) i.val (salts i)
  have width (i : {i // i ∈ positions}) : (record i).length = 528 := lower_record_length false _ _ _
  have length := fixed_flatmap_length record 528 width (honestOrder positions)
  rw [honest_order_length] at length
  have within : 528*ordinal+offset < ((honestOrder positions).flatMap record).length := by rw [length]; omega
  rw [honest_proof_parts, List.getElem?_append_left within]
  exact fixed_flatmap_byte record 528 width (honestOrder positions) ordinal offset
    (by simpa only [honest_order_length]) inside

private theorem honest_frontier_byte (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal offset : Nat)
    (present : ordinal < (Opening.openingNodes positions).length) (inside : offset < 32) :
    (honestCheckInput oracle message positions salts).proof[528*positions.card+32*ordinal+offset]? =
      (digestBytes (honestHeap oracle message salts (Opening.openingNodes positions)[ordinal]))[offset]? := by
  let record := fun i : {i // i ∈ positions} => lowerRecord false (honestHeap oracle message salts) i.val (salts i)
  have length := fixed_flatmap_length record 528 (fun _ => lower_record_length false _ _ _) (honestOrder positions)
  rw [honest_order_length] at length
  rw [honest_proof_parts, List.getElem?_append_right (by rw [length]; omega), length,
    show 528*positions.card+32*ordinal+offset-528*positions.card = 32*ordinal+offset by omega]
  exact fixed_flatmap_byte _ 32 (fun _ => digestBytes_length _) _ ordinal offset present inside

private theorem nonce_byte (heap : Nat → Digest) (index : Index) (salt : BitVec 128)
    (offset : Nat) (inside : offset < 16) :
    (lowerRecord false heap index salt)[offset]? = some (salt.extractLsb' (8*offset) 8) := by
  unfold lowerRecord
  rw [List.getElem?_append_left (by simpa [saltBytes] using inside)]
  simp only [saltBytes, List.getElem?_ofFn, dite_eq_left inside]

private theorem sibling_byte (heap : Nat → Digest) (index : Index) (salt : BitVec 128)
    (level offset : Nat) (levelBound : level < 16) (inside : offset < 32) :
    (lowerRecord false heap index salt)[16+32*level+offset]? =
      some ((heap (((LENGTH+index.val)/2^level) ^^^ 1)).extractLsb' (8*offset) 8) := by
  unfold lowerRecord
  simp only [Bool.false_and, proofDigestBytes, Bool.false_eq_true, ite_false]
  have size : (saltBytes salt).length = 16 := by simp [saltBytes]
  rw [List.getElem?_append_right (by rw [size]; omega), size,
    show 16+32*level+offset-16 = 32*level+offset by omega]
  rw [fixed_flatmap_byte _ 32 (fun _ => digestBytes_length _) _ level offset (by simpa) inside]
  simp only [List.getElem_range, digestBytes, List.getElem?_ofFn, dite_eq_left inside]

theorem honest_input_nonce (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (ordinal : Nat) (present : ordinal < positions.card) :
    readBuffer (Assembly.submission.initialState .check (honestCheckInput oracle message positions salts))
      (Assembly.submission.layout.proof+528*ordinal) 16 = salts (honestIndex positions ordinal present) := by
  let input := honestCheckInput oracle message positions salts
  have decoded := read_serialized_slice (Assembly.submission.initialState .check input)
    (salts (honestIndex positions ordinal present)) (Assembly.submission.layout.proof+528*ordinal) 0 16 (by
      intro offset inside
      have bounded : 528*ordinal+offset < input.proof.length := by
        rw [honest_proof_length]
        unfold Opening.openingLength
        omega
      rw [Nat.add_assoc, check_input_proof_byte input (honest_input_admitted oracle message positions salts) _ bounded]
      have byte := honest_record_byte oracle message positions salts ordinal offset present (by omega)
      rw [nonce_byte _ _ _ offset inside, List.getElem?_eq_getElem bounded, Option.some_inj] at byte
      simpa only [Nat.zero_add] using byte)
  exact decoded.trans BitVec.extractLsb'_eq_self

theorem honest_input_sibling (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (ordinal level : Nat) (present : ordinal < positions.card) (levelBound : level < 16) :
    readBuffer (Assembly.submission.initialState .check (honestCheckInput oracle message positions salts))
      (Assembly.submission.layout.proof+(528*ordinal+16+32*level)) 32 =
      honestHeap oracle message salts (((LENGTH+(honestIndex positions ordinal present).val.val)/2^level) ^^^ 1) := by
  let input := honestCheckInput oracle message positions salts
  let digest := honestHeap oracle message salts (((LENGTH+(honestIndex positions ordinal present).val.val)/2^level) ^^^ 1)
  have decoded := read_serialized_slice (Assembly.submission.initialState .check input) digest
    (Assembly.submission.layout.proof+(528*ordinal+16+32*level)) 0 32 (by
      intro offset inside
      have bounded : 528*ordinal+(16+32*level+offset) < input.proof.length := by
        rw [honest_proof_length]
        unfold Opening.openingLength
        omega
      rw [show Assembly.submission.layout.proof+(528*ordinal+16+32*level)+offset =
        Assembly.submission.layout.proof+(528*ordinal+(16+32*level+offset)) by omega,
        check_input_proof_byte input (honest_input_admitted oracle message positions salts) _ bounded]
      have byte := honest_record_byte oracle message positions salts ordinal (16+32*level+offset) present (by omega)
      rw [sibling_byte _ _ _ level offset levelBound inside, List.getElem?_eq_getElem bounded, Option.some_inj] at byte
      simpa only [Nat.zero_add] using byte)
  exact decoded.trans BitVec.extractLsb'_eq_self

theorem honest_input_frontier (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (ordinal : Nat) (present : ordinal < (Opening.openingNodes positions).length) :
    readBuffer (Assembly.submission.initialState .check (honestCheckInput oracle message positions salts))
      (Assembly.submission.layout.proof+(528*positions.card+32*ordinal)) 32 =
      honestHeap oracle message salts (Opening.openingNodes positions)[ordinal] := by
  let input := honestCheckInput oracle message positions salts
  let digest := honestHeap oracle message salts (Opening.openingNodes positions)[ordinal]
  have decoded := read_serialized_slice (Assembly.submission.initialState .check input) digest
    (Assembly.submission.layout.proof+(528*positions.card+32*ordinal)) 0 32 (by
      intro offset inside
      have bounded : 528*positions.card+32*ordinal+offset < input.proof.length := by
        rw [honest_proof_length]
        unfold Opening.openingLength
        omega
      rw [Nat.add_assoc, check_input_proof_byte input (honest_input_admitted oracle message positions salts) _ bounded]
      have byte := honest_frontier_byte oracle message positions salts ordinal offset present inside
      rw [List.getElem?_eq_getElem bounded] at byte
      simpa only [digest, digestBytes, List.getElem?_ofFn, dite_eq_left inside, Option.some_inj, Nat.zero_add]
        using byte)
  exact decoded.trans BitVec.extractLsb'_eq_self

end TwoPermutationPrototype.Checker
