import CommitGolfCandidate.QuadInputFrame
import CommitGolfCandidate.TwoPermutationPentaSpec

/-! The honest penta proof: 1424-byte records in ascending position order, no
footer. Every record field is read back from the loader's proof buffer. -/
namespace TwoPermutationPrototype.Quad.Honest
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Quad.Checker (honestCheckInput loaderReference)

set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

def honestLeaves (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : DigestTape :=
  pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts

def honestPenta (oracle : Oracle) : PentaFunction :=
  pentaFunction (BiPermutation.equiv Block oracle.permutation).forward

def honestOrder (positions : Positions) : List {index // index ∈ positions} :=
  positions.attach.sort (fun i j => i.val ≤ j.val)

theorem honest_order_length (positions : Positions) : (honestOrder positions).length = positions.card := by
  simp [honestOrder]

def honestIndex (positions : Positions) (ordinal : Nat) (present : ordinal < positions.card) :
    {index // index ∈ positions} :=
  (honestOrder positions)[ordinal]'(by simpa only [honest_order_length] using present)

theorem honest_commitment (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).commitment =
      pentaRoot (honestPenta oracle) (honestLeaves oracle message salts) := rfl

theorem honest_proof_parts (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).proof =
      (honestOrder positions).flatMap (fun i : {i // i ∈ positions} =>
        pentaRecord (honestPenta oracle) (honestLeaves oracle message salts) i.val (salts i.val)) := rfl

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
    (honestCheckInput oracle message positions salts).proof.length = 1424*positions.card := by
  rw [honest_proof_parts, fixed_flatmap_length _ 1424 (fun _ => penta_record_length _ _ _ _) _, honest_order_length]

theorem honest_input_records_fit (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    1424*positions.card ≤ (honestCheckInput oracle message positions salts).proof.length := by
  rw [honest_proof_length]

theorem honest_input_empty (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (empty : positions.card = 0) :
    (honestCheckInput oracle message positions salts).proof.length = 0 := by
  rw [honest_proof_length, empty]

theorem honest_record_byte (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal offset : Nat)
    (present : ordinal < positions.card) (inside : offset < 1424) :
    (honestCheckInput oracle message positions salts).proof[1424*ordinal+offset]? =
      (pentaRecord (honestPenta oracle) (honestLeaves oracle message salts) (honestIndex positions ordinal present)
        (salts (honestIndex positions ordinal present)))[offset]? := by
  rw [honest_proof_parts]
  exact fixed_flatmap_byte _ 1424 (fun _ => penta_record_length _ _ _ _) (honestOrder positions) ordinal offset
    (by simpa only [honest_order_length]) inside

theorem nonce_byte (penta : PentaFunction) (leaves : DigestTape) (index : Index) (salt : BitVec 128)
    (offset : Nat) (inside : offset < 16) :
    (pentaRecord penta leaves index salt)[offset]? = some (salt.extractLsb' (8*offset) 8) := by
  unfold pentaRecord
  rw [List.getElem?_append_left (by simpa [saltBytes] using inside)]
  simp only [saltBytes,List.getElem?_ofFn,dite_eq_left inside]

private theorem level_bytes_length (penta : PentaFunction) (leaves : DigestTape) (index : Index) (k : Nat) :
    ((List.range 4).flatMap fun j => digestBytes (pentaNode penta leaves k (pentaNeighbour index k j))).length = 128 := by
  rw [fixed_flatmap_length _ 32 (fun _ => digestBytes_length _) _]
  rfl

theorem sibling_byte (penta : PentaFunction) (leaves : DigestTape) (index : Index) (salt : BitVec 128)
    (level child offset : Nat) (deep : level<11) (which : child<4) (inside : offset<32) :
    (pentaRecord penta leaves index salt)[16+128*level+32*child+offset]? =
      some ((pentaNode penta leaves level (pentaNeighbour index level child)).extractLsb' (8*offset) 8) := by
  unfold pentaRecord
  rw [List.getElem?_append_right (by simp [saltBytes]; omega),show (saltBytes salt).length=16 by simp [saltBytes],
    show 16+128*level+32*child+offset-16=128*level+(32*child+offset) by omega]
  rw [fixed_flatmap_byte _ 128 (level_bytes_length penta leaves index) _ level _ (by simpa [PENTA_LEVELS] using deep)
    (by omega)]
  rw [List.getElem_range]
  rw [fixed_flatmap_byte _ 32 (fun _ => digestBytes_length _) _ child offset (by simpa using which) inside]
  rw [List.getElem_range]
  simp only [digestBytes,List.getElem?_ofFn,dite_eq_left inside]

theorem honest_input_admitted (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).proof.length ≤ loaderReference.sizes.proof := by
  rw [honest_proof_length]
  have cardinal : positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ positions
  change 1424*positions.card≤1424*2^24
  change positions.card≤16777216 at cardinal
  omega

private theorem read_field {bits : Nat} (input : CheckInput)
    (valid : input.proof.length ≤ loaderReference.sizes.proof)
    (value : BitVec bits) (start count : Nat) (within : start+count ≤ input.proof.length)
    (serialized : ∀ j, j<count → input.proof[start+j]? = some (value.extractLsb' (8*j) 8)) :
    readBuffer (loaderReference.initialState .check input)
      (loaderReference.layout.proof+start) count = value.extractLsb' 0 (8*count) := by
  apply read_serialized_slice _ value _ 0 count
  intro j small
  have bounded : start+j < input.proof.length := by omega
  rw [Nat.add_assoc, Checker.check_input_proof_byte input valid _ bounded]
  have byte := serialized j small
  rw [List.getElem?_eq_getElem bounded, Option.some_inj] at byte
  simpa only [Nat.zero_add] using byte

theorem honest_input_nonce (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) :
    readBuffer (loaderReference.initialState .check (honestCheckInput oracle message positions salts))
      (loaderReference.layout.proof+1424*ordinal) 16 = salts (honestIndex positions ordinal present) := by
  have enough := honest_input_records_fit oracle message positions salts
  have bytes := read_field (honestCheckInput oracle message positions salts)
    (honest_input_admitted oracle message positions salts) (salts (honestIndex positions ordinal present))
    (1424*ordinal) 16 (by omega) (by
      intro j bound
      rw [honest_record_byte oracle message positions salts _ _ present (by omega),nonce_byte _ _ _ _ j bound])
  exact bytes.trans BitVec.extractLsb'_eq_self

theorem honest_input_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal level child : Nat) (present : ordinal<positions.card)
    (deep : level<11) (which : child<4) :
    readBuffer (loaderReference.initialState .check (honestCheckInput oracle message positions salts))
      (loaderReference.layout.proof+(1424*ordinal+16+128*level+32*child)) 32 =
      pentaNode (honestPenta oracle) (honestLeaves oracle message salts) level
        (pentaNeighbour (honestIndex positions ordinal present) level child) := by
  have enough := honest_input_records_fit oracle message positions salts
  have bytes := read_field (honestCheckInput oracle message positions salts)
    (honest_input_admitted oracle message positions salts) _ (1424*ordinal+16+128*level+32*child) 32 (by omega) (by
      intro j bound
      rw [show 1424*ordinal+16+128*level+32*child+j=1424*ordinal+(16+128*level+32*child+j) by omega,
        honest_record_byte oracle message positions salts _ _ present (by omega),
        sibling_byte _ _ _ _ level child j deep which bound])
  exact bytes.trans BitVec.extractLsb'_eq_self

end TwoPermutationPrototype.Quad.Honest
