import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.InputOrder
import CommitGolfCandidate.TwoPermutationPackedTrustedInput
import CommitGolfCandidate.TwoPermutationPackedCertificate
import CommitGolfCandidate.TwoPermutationPackedOpeningSchedule
import CommitGolfCandidate.TwoPermutationPackedOpeningProofBytes

namespace TwoPermutationPrototype.PackedHonest
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.PackedCertificate (honestCheckInput)

set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

def honestHeap (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → Digest :=
  transcriptHeap true oracle.compression
    (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)

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
        lowerRecord true (honestHeap oracle message salts) i.val (salts i.val)) ++
      (Opening.openingNodes positions).flatMap (fun node => proofDigestBytes true (honestHeap oracle message salts node)) := by
  change _ ++ frontierProof true _ ((honestOrder positions).map (capGroup ∘ Subtype.val)) = _
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
    (honestCheckInput oracle message positions salts).proof.length = PackedOpening.proofLength positions := by
  rw [honest_proof_parts, List.length_append,
    fixed_flatmap_length _ 498 (fun _ => lower_record_length true _ _ _) _,
    fixed_flatmap_length _ 30 (fun _ => proof_digest_length true _) _, honest_order_length]
  rfl

theorem honest_input_records_fit (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    498*positions.card ≤ (honestCheckInput oracle message positions salts).proof.length := by
  rw [honest_proof_length]
  exact Nat.le_add_right _ _

theorem honest_input_empty (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (empty : positions.card = 0) :
    (honestCheckInput oracle message positions salts).proof.length = 0 := by
  rw [honest_proof_length]
  simp [PackedOpening.proofLength, Opening.openingNodes, empty]

theorem honest_record_byte (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal offset : Nat)
    (present : ordinal < positions.card) (inside : offset < 498) :
    (honestCheckInput oracle message positions salts).proof[498*ordinal+offset]? =
      (lowerRecord true (honestHeap oracle message salts) (honestIndex positions ordinal present)
        (salts (honestIndex positions ordinal present)))[offset]? := by
  let record := fun i : {i // i ∈ positions} => lowerRecord true (honestHeap oracle message salts) i.val (salts i)
  have width (i : {i // i ∈ positions}) : (record i).length = 498 := lower_record_length true _ _ _
  have length := fixed_flatmap_length record 498 width (honestOrder positions)
  rw [honest_order_length] at length
  have within : 498*ordinal+offset < ((honestOrder positions).flatMap record).length := by rw [length]; omega
  rw [honest_proof_parts, List.getElem?_append_left within]
  exact fixed_flatmap_byte record 498 width (honestOrder positions) ordinal offset
    (by simpa only [honest_order_length]) inside

theorem honest_frontier_byte (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal offset : Nat)
    (present : ordinal < (Opening.openingNodes positions).length) (inside : offset < 30) :
    (honestCheckInput oracle message positions salts).proof[498*positions.card+30*ordinal+offset]? =
      (proofDigestBytes true (honestHeap oracle message salts (Opening.openingNodes positions)[ordinal]))[offset]? := by
  let record := fun i : {i // i ∈ positions} => lowerRecord true (honestHeap oracle message salts) i.val (salts i)
  have length := fixed_flatmap_length record 498 (fun _ => lower_record_length true _ _ _) (honestOrder positions)
  rw [honest_order_length] at length
  rw [honest_proof_parts, List.getElem?_append_right (by rw [length]; omega), length,
    show 498*positions.card+30*ordinal+offset-498*positions.card = 30*ordinal+offset by omega]
  exact fixed_flatmap_byte _ 30 (fun _ => proof_digest_length true _) _ ordinal offset present inside

theorem nonce_byte (heap : Nat → Digest) (index : Index) (salt : BitVec 128)
    (offset : Nat) (inside : offset < 16) :
    (lowerRecord true heap index salt)[offset]? = some (salt.extractLsb' (8*offset) 8) := by
  unfold lowerRecord
  rw [List.getElem?_append_left (by simpa [saltBytes] using inside)]
  simp only [saltBytes, List.getElem?_ofFn, dite_eq_left inside]


theorem record_fields (heap : Nat → Digest) (index : Index) (salt : BitVec 128) :
    lowerRecord true heap index salt =
      saltBytes salt ++ digestBytes (heap ((LENGTH+index.val) ^^^ 1)) ++
        (List.range 15).flatMap (fun j => proofDigestBytes true (heap (Opening.lowerNode index (j+1) ^^^ 1))) := by
  unfold lowerRecord
  rw [show List.range 16 = 0 :: (List.range 15).map (fun j => j+1) by decide,
    List.flatMap_cons, List.flatMap_map]
  simp [Opening.lowerNode, proofDigestBytes, List.append_assoc]

theorem first_sibling_byte (heap : Nat → Digest) (index : Index) (salt : BitVec 128)
    (offset : Nat) (inside : offset < 32) :
    (lowerRecord true heap index salt)[16+offset]? =
      some ((heap ((LENGTH+index.val) ^^^ 1)).extractLsb' (8*offset) 8) := by
  rw [record_fields, List.append_assoc, List.getElem?_append_right (by simp [saltBytes])]
  rw [show (saltBytes salt).length=16 by simp [saltBytes], Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simpa only [digestBytes_length] using inside)]
  simp only [digestBytes, List.getElem?_ofFn, dite_eq_left inside]

theorem later_sibling_byte (heap : Nat → Digest) (index : Index) (salt : BitVec 128)
    (ordinal offset : Nat) (hasSibling : ordinal < 15) (inside : offset < 30) :
    (lowerRecord true heap index salt)[48+30*ordinal+offset]? =
      some ((heap (Opening.lowerNode index (ordinal+1) ^^^ 1)).extractLsb' (8*offset) 8) := by
  rw [record_fields, List.getElem?_append_right (by simp [saltBytes, digestBytes_length] <;> omega)]
  have width : (saltBytes salt ++ digestBytes (heap ((LENGTH+index.val) ^^^ 1))).length = 48 := by
    simp [saltBytes, digestBytes_length]
  rw [width, show 48+30*ordinal+offset-48 = 30*ordinal+offset by omega]
  rw [fixed_flatmap_byte _ 30 (fun _ => proof_digest_length true _) _ ordinal offset (by simpa using hasSibling) inside]
  rw [List.getElem_range]
  simp only [proofDigestBytes, ite_true, List.getElem?_take, if_pos inside,
    digestBytes, List.getElem?_ofFn, Nat.lt_trans inside (by decide : 30<32), dite_true]

theorem honest_projected_node (compress : Compression) (leaves : DigestTape) (node : Nat)
    (pos : 0<node) (internal : node<LENGTH) :
    (0#16) ++ (transcriptHeap true compress leaves node).extractLsb' 0 240 =
      transcriptHeap true compress leaves node := by
  rw [transcript_heap_parent true compress leaves node pos internal]
  simp [projectInternal]
  rw [BitVec.extractLsb'_append_eq_right]

theorem honest_input_admitted (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).proof.length ≤ PackedChecker.submission.sizes.proof := by
  rw [honest_proof_length]
  exact (PackedOpening.proof_fits_every_cardinality positions).trans (by decide)

private theorem read_field {bits : Nat} (input : CheckInput)
    (valid : input.proof.length ≤ PackedChecker.submission.sizes.proof)
    (value : BitVec bits) (start count : Nat) (within : start+count ≤ input.proof.length)
    (serialized : ∀ j, j<count → input.proof[start+j]? = some (value.extractLsb' (8*j) 8)) :
    readBuffer (PackedChecker.submission.initialState .check input)
      (PackedChecker.submission.layout.proof+start) count = value.extractLsb' 0 (8*count) := by
  apply read_serialized_slice _ value _ 0 count
  intro j small
  have bounded : start+j < input.proof.length := by omega
  rw [Nat.add_assoc, PackedChecker.check_input_proof_byte input valid _ bounded]
  have byte := serialized j small
  rw [List.getElem?_eq_getElem bounded, Option.some_inj] at byte
  simpa only [Nat.zero_add] using byte

theorem honest_input_nonce (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) :
    readBuffer (PackedChecker.submission.initialState .check (honestCheckInput oracle message positions salts))
      (PackedChecker.submission.layout.proof+498*ordinal) 16 = salts (honestIndex positions ordinal present) := by
  have enough := honest_input_records_fit oracle message positions salts
  have bytes := read_field (honestCheckInput oracle message positions salts)
    (honest_input_admitted oracle message positions salts) (salts (honestIndex positions ordinal present))
    (498*ordinal) 16 (by omega) (by
      intro j bound
      rw [honest_record_byte oracle message positions salts _ _ present (by omega),nonce_byte _ _ _ j bound])
  exact bytes.trans BitVec.extractLsb'_eq_self

theorem honest_input_first_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) :
    readBuffer (PackedChecker.submission.initialState .check (honestCheckInput oracle message positions salts))
      (PackedChecker.submission.layout.proof+(498*ordinal+16)) 32 =
      honestHeap oracle message salts ((LENGTH+(honestIndex positions ordinal present).val.val) ^^^ 1) := by
  have enough := honest_input_records_fit oracle message positions salts
  have bytes := read_field (honestCheckInput oracle message positions salts)
    (honest_input_admitted oracle message positions salts) _ (498*ordinal+16) 32 (by omega) (by
      intro j bound
      rw [Nat.add_assoc, honest_record_byte oracle message positions salts _ _ present (by omega),
        first_sibling_byte _ _ _ j bound])
  exact bytes.trans BitVec.extractLsb'_eq_self

theorem honest_input_later_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal sibling : Nat) (present : ordinal < positions.card) (later : sibling<15) :
    readBuffer (PackedChecker.submission.initialState .check (honestCheckInput oracle message positions salts))
      (PackedChecker.submission.layout.proof+(498*ordinal+48+30*sibling)) 30 =
      (honestHeap oracle message salts (Opening.lowerNode (honestIndex positions ordinal present) (sibling+1) ^^^ 1)).extractLsb' 0 240 := by
  have enough := honest_input_records_fit oracle message positions salts
  apply read_field _ (honest_input_admitted oracle message positions salts) _ _ _ (by omega)
  intro j bound
  rw [show 498*ordinal+48+30*sibling+j=498*ordinal+(48+30*sibling+j) by omega,
    honest_record_byte oracle message positions salts _ _ present (by omega),
    later_sibling_byte _ _ _ sibling j later bound]

theorem honest_frontier_digest (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < (Opening.openingNodes positions).length) :
    readBuffer (PackedChecker.submission.initialState .check (honestCheckInput oracle message positions salts))
      (PackedChecker.submission.layout.proof+(498*positions.card+30*ordinal)) 30 =
      (honestHeap oracle message salts (Opening.openingNodes positions)[ordinal]).extractLsb' 0 240 := by
  have length := honest_proof_length oracle message positions salts
  have enough : 498*positions.card+30*ordinal+30 ≤ (honestCheckInput oracle message positions salts).proof.length := by
    rw [length]
    unfold PackedOpening.proofLength PackedOpening.recordBytes
    omega
  apply read_field _ (honest_input_admitted oracle message positions salts) _ _ _ enough
  intro j bound
  rw [honest_frontier_byte oracle message positions salts ordinal j present bound]
  simp only [proofDigestBytes, ite_true, List.getElem?_take, if_pos bound,
    digestBytes, List.getElem?_ofFn, Nat.lt_trans bound (by decide : 30<32), dite_true]

end TwoPermutationPrototype.PackedHonest
